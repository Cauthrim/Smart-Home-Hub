import java.io.IOException;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.util.*;
import java.util.stream.IntStream;

/**
 * Smart home hub emulator.
 *
 * @author Denis Karpov
 * @version 1.0
 */
public class SmartHub {
    //By my calculations, even if the hub sends billions of requests a day, long-typed serial
    //number counter can still service it for ~1e8 days, so there is no need to complicate it.
    private static long serialCount = 1;
    private static String serverPort;
    private static byte[] crcTable;
    private static int hubAddress;
    private static long time = 0;
    private static long startTime = 0;
    private static final Map<String, Integer> deviceAddresses = new HashMap<>();
    private static final Map<Integer, List<String>> switchDevices = new HashMap<>();
    private static final Map<Integer, List<SensorProperties>> sensorProps = new HashMap<>();
    private static final Map<Integer, Queue<Long>> deviceRequests = new HashMap<>();
    private static final Map<Integer, Byte> deviceTypes = new HashMap<>();
    private static final int MASK_DATA = 0x7f;
    private static final int MASK_CONTINUE = 0x80;
    private static final int HTTP_OK = 200;
    private static final int HTTP_FINISH = 204;
    private static final int ERROR_RETURN = 99;
    private static final int BROADCAST_DST = 65407;
    private static final byte[] hubName = {3, 104, 117, 98};
    private static HttpClient connection;

    /**
     * Internal representation of the payload of a packet.
     */
    private static class Payload {
        int src;
        int dst;
        byte[] serial;
        byte devType;
        byte cmd;
        byte[] cmdBody;

        public Payload(int src, int dst, byte[] serial, byte devType, byte cmd, byte[] cmdBody) {
            this.src = src;
            this.dst = dst;
            this.serial = serial;
            this.devType = devType;
            this.cmd = cmd;
            this.cmdBody = cmdBody;
        }

        /**
         * Method which creates a ready for sending String representation of a packet with this payload.
         *
         * @return the String data.
         */
        public byte[] convertToPacket() {
            byte[] srcBytes = intToBytes(src);
            byte[] dstBytes = intToBytes(dst);
            int varLen = srcBytes.length + dstBytes.length;
            byte[] data = new byte[varLen + serial.length + 2 + cmdBody.length];

            System.arraycopy(srcBytes, 0, data, 0, srcBytes.length);
            System.arraycopy(dstBytes, 0, data, srcBytes.length, dstBytes.length);

            System.arraycopy(serial, 0, data, varLen, serial.length);

            data[varLen + serial.length] = devType;
            data[varLen + serial.length + 1] = cmd;

            System.arraycopy(cmdBody, 0, data, varLen + 2 + serial.length, cmdBody.length);

            byte[] packet = new byte[data.length + 2];
            packet[0] = (byte) (data.length);
            packet[packet.length - 1] = computeCRC8(data);
            System.arraycopy(data, 0, packet, 1, data.length);
            return packet;
        }
    }

    /**
     * Internal representation of Sensor properties.
     */
    private static class SensorProperties {
        byte op;
        long value;
        String name;

        public SensorProperties(byte op, long value, String name) {
            this.op = op;
            this.value = value;
            this.name = name;
        }
    }

    /**
     * Converts int as two bytes into big endian byte array.
     *
     * @param x - integer to convert.
     * @return the byte array.
     */
    private static byte[] intToBytes(int x) {
        if (x < (1 << 8)) {
            return new byte[] {(byte) x};
        } else {
            return new byte[] {(byte) (x / (1 << 8)), (byte) (x % (1 << 8))};
        }
    }

    /**
     * Converts Java's signed byte into int to get unsigned value.
     *
     * @param b - byte to convert.
     * @return the unsigned value in int.
     */
    private static int byteToInt(byte b) {
        return b >= 0 ? b : 256 + b;
    }

    /**
     * Converts byte array into int.
     *
     * @param bytes to convert.
     * @return the result of conversion.
     */
    private static int byteArrayToInt(byte[] bytes) {
        int value = 0;
        for (byte b : bytes) {
            value = (value << 8) + (b & 0xFF);
        }
        return value;
    }

    /**
     * Precalculates CRC8 lookup table.
     */
    private static void calculateCRCTable() {
        byte generator = 0x1D;
        crcTable = new byte[256];

        /* iterate over all byte values 0 - 255 */
        for (int dividend = 0; dividend < 256; dividend++) {
            byte currByte = (byte) dividend;

            /* calculate the CRC-8 value for current byte */
            for (byte bit = 0; bit < 8; bit++) {
                if ((currByte & 0x80) != 0) {
                    currByte <<= 1;
                    currByte ^= generator;
                } else {
                    currByte <<= 1;
                }
            }

            /* store CRC value in lookup table */
            crcTable[dividend] = currByte;
        }
    }

    /**
     * Computes CRC8 of given bytes.
     *
     * @param bytes - to compute CRC8 for.
     * @return the CRC8 checksum.
     */
    private static byte computeCRC8(byte[] bytes) {
        byte crc = 0;

        for (byte b : bytes) {
            /* XOR-in next input byte */
            byte data = (byte) (b ^ crc);

            int ind = byteToInt(data);
            /* get current CRC value = remainder */
            crc = crcTable[ind];
        }

        return crc;
    }

    /**
     * Converts numeric value into ULEB128.
     *
     * @param value - to convert.
     * @return bytes of value converted into ULEB128.
     */
    private static byte[] encodeULEB128(long value) {
        ArrayList<Byte> bytes = new ArrayList<>();
        do {
            byte group = (byte) (value & MASK_DATA);

            value >>= 7;
            if (value != 0) {
                group |= MASK_CONTINUE;
            }

            bytes.add(group);
        } while (value != 0);

        byte[] newBytes = new byte[bytes.size()];
        IntStream.range(0, bytes.size()).forEach(ind -> newBytes[ind] = bytes.get(ind));

        return newBytes;
    }

    /**
     * Decoding of ULEB128 into long.
     *
     * @param bytes - ULEB128 representation to decode.
     * @return the decoded long value.
     */
    private static long decodeULEB128(byte[] bytes) {
        long value = 0;
        int bitSize = 0;

        for (byte b : bytes) {
            value += ((long) b & MASK_DATA) << bitSize;
            bitSize += 7;
        }

        return value;
    }

    /**
     * Sets {@code hubAddress} by converting hex string input into ULEB128 bytes.
     *
     * @param hex - hexadecimal representation of hub's address.
     */
    private static void getHubAddress(String hex) {
        long numAddress = Long.parseLong(hex, 16);
        byte[] addressBytes = encodeULEB128(numAddress);
        hubAddress = byteToInt(addressBytes[0]);
        if (addressBytes.length == 2) {
            hubAddress = (byteToInt(addressBytes[0]) << 8) + byteToInt(addressBytes[1]);
        }
    }

    /**
     * Converts data into URL-encoded Base64 String.
     *
     * @param data - data to convert.
     * @return converted data.
     */
    private static String encodeForUrl(byte[] data) {
        return Base64.getUrlEncoder().encodeToString(data).replace("=", "");
    }

    /**
     * Checks for status code scenarios, extracted to increase clarity.
     *
     * @param response - response to get the status code from.
     */
    private static void checkStatusCode(HttpResponse<String> response) {
        if (response.statusCode() == HTTP_FINISH) {
            System.exit(0);
        }
        if (response.statusCode() != HTTP_OK) {
            System.exit(ERROR_RETURN);
        }
    }

    /**
     * Method to convert binary response data into separated packet payloads.
     *
     * @param responseBytes - the binary response data.
     */
    private static List<Payload> extractPackets(byte[] responseBytes) {
        int ind = 0;
        ArrayList<Payload> payloads = new ArrayList<>();

        while (ind < responseBytes.length) {
            int payloadLen = byteToInt(responseBytes[ind]);
            byte[] currentPayload = new byte[payloadLen];
            final int bound = ind + 1;

            System.arraycopy(responseBytes, bound, currentPayload, 0, payloadLen);
            if (computeCRC8(currentPayload) != responseBytes[ind + payloadLen + 1]) {
                ind = ind + payloadLen + 2;
                continue;
            }

            int varIntInd = 0;
            byte[][] vars = new byte[3][];
            ArrayList<Byte> varList = new ArrayList<>();
            for (int i = 0; i < 3; i++) {
                for (; currentPayload[varIntInd] < 0; varIntInd++) {
                    varList.add(currentPayload[varIntInd]);
                }
                varList.add(currentPayload[varIntInd]);
                varIntInd++;

                vars[i] = new byte[varList.size()];
                for (int j = 0; j < varList.size(); j++) {
                    vars[i][j] = varList.get(j);
                }

                varList.clear();
            }

            byte[] cmdBody = new byte[payloadLen - varIntInd - 2];
            System.arraycopy(currentPayload, varIntInd + 2, cmdBody, 0, cmdBody.length);

            Payload payload = new Payload(
                    byteArrayToInt(vars[0]),
                    byteArrayToInt(vars[1]),
                    vars[2],
                    currentPayload[varIntInd],
                    currentPayload[varIntInd + 1],
                    cmdBody
            );

            payloads.add(payload);

            ind += payloadLen + 2;
        }

        return payloads;
    }

    /**
     * General method for sending POST request to server.
     *
     * @param data - the data to fill the POST request.
     */
    private static List<Payload> send(String data) {
        HttpRequest request = HttpRequest.newBuilder().uri(URI.create(serverPort)).POST(
                HttpRequest.BodyPublishers.ofString(data)).build();
        try {
            HttpResponse<String> response = connection.send(request, HttpResponse.BodyHandlers.ofString());

            checkStatusCode(response);

            try {
                return extractPackets(Base64.getUrlDecoder().decode(response.body()));
            } catch (IllegalArgumentException e) {
                return List.of();
            }
        } catch (IOException | InterruptedException e) {
            System.exit(ERROR_RETURN);
        }

        return null;
    }

    /**
     * Generalized generation of a request.
     *
     * @param deviceAddress - address of dst device.
     * @param deviceType - type of dst device.
     * @param command - request command.
     * @param commandBody - the body of command.
     * @return request in String form.
     */
    private static byte[] readyRequest(int deviceAddress, byte deviceType, byte command, byte[] commandBody) {
        Payload request = new Payload(hubAddress, deviceAddress, encodeULEB128(serialCount), deviceType, command,
                commandBody);
        serialCount++;
        return request.convertToPacket();
    }

    /**
     * Creation of WHOISHERE request to access other devices.
     */
    private static byte[] readyWhoIsHere() {
        return readyRequest(BROADCAST_DST, (byte) 1, (byte) 1, hubName);
    }

    /**
     * Creation of GETSTATUS request.
     *
     * @param deviceAddress - address of dst device.
     * @param deviceType - type of dst device.
     * @return request in String form.
     */
    private static byte[] readyGetStatus(int deviceAddress, byte deviceType) {
        deviceRequests.get(deviceAddress).add(time);
        return readyRequest(deviceAddress, deviceType, (byte) 3, new byte[0]);
    }

    /**
     * Creation of IAMHERE request.
     *
     * @return request in String form.
     */
    private static byte[] readyIAmHere() {
        return readyRequest(BROADCAST_DST, (byte) 1, (byte) 2, hubName);
    }

    /**
     * Creation of SETSTATUS request.
     *
     * @param deviceAddress - the address of device to change status.
     * @param deviceType - the type of device.
     * @param onOrOff - 0 to turn the device off, 1 to turn on.
     * @return request in String form.
     */
    private static byte[] readySetStatus(int deviceAddress, byte deviceType, byte onOrOff) {
        deviceRequests.get(deviceAddress).add(time);
        return readyRequest(deviceAddress, deviceType, (byte) 5, new byte[] {onOrOff});
    }

    private static boolean checkResponsiveness(int address) {
        if (deviceTypes.containsKey(address)) {
            if (!deviceRequests.get(address).isEmpty()) {
                if (time - deviceRequests.get(address).peek() > 300) {
                    deviceTypes.remove(address);
                    return false;
                }
                return true;
            }
            return true;
        }
        return false;
    }

    /**
     * Handles responses pertaining to Environment Sensor devices.
     *
     * @param payload - response payload.
     * @param request - to add possible request to.
     */
    private static void handleEnvSensor(Payload payload, List<Byte> request) {
        if (checkResponsiveness(payload.src)) {
            if (!deviceRequests.get(payload.src).isEmpty()) {
                deviceRequests.get(payload.src).remove();
            }
        } else {
            return;
        }

        int numVal = payload.cmdBody[0];
        int varIntInd = 1;
        byte[][] vals = new byte[numVal][];
        ArrayList<Byte> varList = new ArrayList<>();
        for (int i = 0; i < numVal; i++) {
            for (; payload.cmdBody[varIntInd] < 0; varIntInd++) {
                varList.add(payload.cmdBody[varIntInd]);
            }
            varList.add(payload.cmdBody[varIntInd]);
            varIntInd++;

            vals[i] = new byte[varList.size()];
            for (int j = 0; j < varList.size(); j++) {
                vals[i][j] = varList.get(j);
            }

            varList.clear();
        }

        List<SensorProperties> sensorProperties = sensorProps.get(payload.src);
        for (int i = 0; i < numVal; i++) {
            long decodedVal = decodeULEB128(vals[i]);
            if (((sensorProperties.get(i).op & 2) == 2 && decodedVal > sensorProperties.get(i).value)
                    || ((sensorProperties.get(i).op & 2) == 0 && decodedVal < sensorProperties.get(i).value)) {
                if (deviceAddresses.containsKey(sensorProperties.get(i).name)) {
                    int address = deviceAddresses.get(sensorProperties.get(i).name);
                    if (checkResponsiveness(address)) {
                        byte[] setStatus = readySetStatus(address, deviceTypes.get(address),
                                (byte) (sensorProperties.get(i).op & 1));
                        for (byte b : setStatus) {
                            request.add(b);
                        }
                    }
                }
            }
        }
    }

    /**
     * Handles responses pertaining to Switch devices.
     *
     * @param payload - response payload.
     * @param request - to add possible request to.
     */
    private static void handleSwitch(Payload payload, List<Byte> request) {
        if (checkResponsiveness(payload.src)) {
            if (!deviceRequests.get(payload.src).isEmpty()) {
                deviceRequests.get(payload.src).remove();
            }
        } else {
            return;
        }

        for (String deviceName : switchDevices.get(payload.src)) {
            if (deviceAddresses.containsKey(deviceName)) {
                int address = deviceAddresses.get(deviceName);
                if (checkResponsiveness(address)) {
                    byte[] setStatus = readySetStatus(address, deviceTypes.get(address), payload.cmdBody[0]);
                    for (byte status : setStatus) {
                        request.add(status);
                    }
                }
            }
        }
    }

    /**
     * Handles responses pertaining to Lamp and Socket devices.
     *
     * @param payload - response payload.
     */
    private static void handleLampAndSocket(Payload payload) {
        if (checkResponsiveness(payload.src)) {
            if (!deviceRequests.get(payload.src).isEmpty()) {
                deviceRequests.get(payload.src).remove();
            }
        }
    }

    /**
     * Method for handling IAMHERE and WHOISHERE requests.
     *
     * @param payload - payload of the request.
     * @param request - to add potential responses.
     */
    private static void handleHereRequests(Payload payload, List<Byte> request) {
        if (startTime != 0 && payload.cmd == 2 && time - startTime > 300) {
            return;
        }

        byte[] name = new byte[byteToInt(payload.cmdBody[0])];
        System.arraycopy(payload.cmdBody, 1, name, 0, name.length);
        deviceAddresses.put(new String(name), payload.src);
        deviceTypes.put(payload.src, payload.devType);
        deviceRequests.put(payload.src, new ArrayDeque<>());

        if (payload.cmd == 1) {
            byte[] iAmHere = readyIAmHere();
            for (byte b : iAmHere) {
                request.add(b);
            }
        }
        if (payload.devType == 2 || payload.devType == 3) {
            if (payload.devType == 2) {
                int devInd = name.length + 2;
                int propsLen = byteToInt(payload.cmdBody[devInd]);
                devInd++;

                sensorProps.put(payload.src, new ArrayList<>());
                ArrayList<Byte> valList = new ArrayList<>();
                for (int i = 0; i < propsLen; i++) {
                    byte op = payload.cmdBody[devInd];
                    devInd++;

                    for (; payload.cmdBody[devInd] < 0; devInd++) {
                        valList.add(payload.cmdBody[devInd]);
                    }
                    valList.add(payload.cmdBody[devInd]);
                    devInd++;

                    byte[] val = new byte[valList.size()];
                    for (int j = 0; j < valList.size(); j++) {
                        val[j] = valList.get(j);
                    }
                    valList.clear();

                    int devNameLength = byteToInt(payload.cmdBody[devInd]);
                    devInd++;
                    byte[] devName = new byte[devNameLength];
                    System.arraycopy(payload.cmdBody, devInd, devName, 0, devNameLength);
                    sensorProps.get(payload.src).add(new SensorProperties(op, decodeULEB128(val), new String(devName)));
                    devInd += devNameLength;
                }
            }
            if (payload.devType == 3) {
                List<String> devices = new ArrayList<>();
                int devInd = name.length + 1;
                int devLen = byteToInt(payload.cmdBody[devInd]);
                devInd++;

                for (int i = 0; i < devLen; i++) {
                    int currentNameLen = byteToInt(payload.cmdBody[devInd]);
                    byte[] currentName = new byte[currentNameLen];
                    System.arraycopy(payload.cmdBody, devInd + 1, currentName, 0, currentNameLen);
                    devices.add(new String(currentName));
                    devInd += currentNameLen + 1;
                }

                switchDevices.put(payload.src, devices);
            }
            byte[] getStatus = readyGetStatus(payload.src, payload.devType);
            for (byte b : getStatus) {
                request.add(b);
            }
        }
    }

    /**
     * Global method of continuous workflow of the hub. Constantly sends and receives data.
     */
    private static void start() {
        List<Byte> request = new ArrayList<>();
        List<Payload> payloadList = new ArrayList<>();
        byte[] whoIsHere = readyWhoIsHere();
        for (byte b : whoIsHere) {
            request.add(b);
        }

        while (true) {
            for (Payload payload : payloadList) {
                if (payload.cmd == 6) {
                    time = decodeULEB128(payload.cmdBody);
                    if (startTime == 0) {
                        startTime = time;
                    }
                }
            }
            for (Payload payload : payloadList) {
                if (payload.cmd == 2 || payload.cmd == 1) {
                    if (payload.cmd == 2 && time - startTime > 300) {
                        continue;
                    }
                    handleHereRequests(payload, request);
                    continue;
                }

                switch (payload.devType) {
                    case 2 -> handleEnvSensor(payload, request);
                    case 3 -> handleSwitch(payload, request);
                    case 4, 5 -> handleLampAndSocket(payload);
                }
            }



            byte[] byteRequest = new byte[request.size()];
            for (int i = 0; i < request.size(); i++) {
                byteRequest[i] = request.get(i);
            }
            payloadList = send(encodeForUrl(byteRequest));

            request.clear();
        }
    }

    /**
     * Initializing method.
     *
     * @param args - server URL address and hub 14-bit address.
     */
    public static void main(String[] args) {
        serverPort = args[0];
        getHubAddress(args[1]);
        calculateCRCTable();
        connection = HttpClient.newHttpClient();
        start();
    }
}