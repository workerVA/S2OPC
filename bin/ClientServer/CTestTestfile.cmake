# CMake generated Testfile for 
# Source directory: S2OPC_ROOT_DIR/tests/ClientServer
# Build directory: S2OPC_ROOT_DIR/tests/ClientServer
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(unit::check_helpers "S2OPC_ROOT_DIR/bin/check_helpers")
set_tests_properties(unit::check_helpers PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=check_helpers.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(unit::check_sockets "S2OPC_ROOT_DIR/bin/check_sockets")
set_tests_properties(unit::check_sockets PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=check_sockets.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(unit::check_sc_rcv_buffer "S2OPC_ROOT_DIR/bin/check_sc_rcv_buffer")
set_tests_properties(unit::check_sc_rcv_buffer PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=check_sc_rcv_buffer.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(unit::check_sc_rcv_encrypted_buffer "S2OPC_ROOT_DIR/bin/check_sc_rcv_encrypted_buffer")
set_tests_properties(unit::check_sc_rcv_encrypted_buffer PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=check_sc_rcv_encrypted_buffer.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(unit::toolkit_test_server_client "S2OPC_ROOT_DIR/bin/toolkit_test_server_client")
set_tests_properties(unit::toolkit_test_server_client PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=toolkit_test_server_client.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(unit::toolkit_test_server_local_service "python3" "S2OPC_ROOT_DIR/tests/scripts/tap-wrap.py" "S2OPC_ROOT_DIR/bin/toolkit_test_server_local_service")
set_tests_properties(unit::toolkit_test_server_local_service PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=toolkit_test_server_local_service.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::client_server_test "python3" "S2OPC_ROOT_DIR/tests/scripts/tap-wrap.py" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/toolkit_test_nano_server" "S2OPC_ROOT_DIR/bin/toolkit_test_client")
set_tests_properties(validation::client_server_test PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=client_server_test.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::client_service_faults_test "python3" "S2OPC_ROOT_DIR/tests/scripts/tap-wrap.py" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/toolkit_test_nano_server" "S2OPC_ROOT_DIR/bin/toolkit_test_client_service_faults")
set_tests_properties(validation::client_service_faults_test PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=client_service_faults_test.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::client.py "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/toolkit_test_nano_server client" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/interop_tools/client.py")
set_tests_properties(validation::client.py PROPERTIES  WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::client_sc_renew.py "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/toolkit_test_nano_server client_sc_renew" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/interop_tools/client_sc_renew.py")
set_tests_properties(validation::client_sc_renew.py PROPERTIES  WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::client_session_timeout.py "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/toolkit_test_nano_server client_session_timeout" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/interop_tools/client_session_timeout.py")
set_tests_properties(validation::client_session_timeout.py PROPERTIES  WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::client_sc_establish_timeout.py "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/toolkit_test_nano_server client_sc_establish_timeout" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/interop_tools/client_sc_establish_timeout.py")
set_tests_properties(validation::client_sc_establish_timeout.py PROPERTIES  WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::toolkit_test_suite_client "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/tests/ClientServer/interop_tools" "--server-cmd" "python3 S2OPC_ROOT_DIR/tests/ClientServer/interop_tools/server.py 25000" "./toolkit_test_suite_client")
set_tests_properties(validation::toolkit_test_suite_client PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=toolkit_test_suite_client.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::secure_channel_level::SignAndEncrypt_B256Sha256_2048bit "python3" "S2OPC_ROOT_DIR/tests/scripts/tap-wrap.py" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/test_secure_channels_server 2048" "--wait-server" "S2OPC_ROOT_DIR/bin/test_secure_channels_client")
set_tests_properties(validation::secure_channel_level::SignAndEncrypt_B256Sha256_2048bit PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=secure_channel_level_SignAndEncrypt_B256Sha256_2048bit.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::secure_channel_level::Sign_B256Sha256_2048bit "python3" "S2OPC_ROOT_DIR/tests/scripts/tap-wrap.py" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/test_secure_channels_server 2048" "--wait-server" "S2OPC_ROOT_DIR/bin/test_secure_channels_client" "sign")
set_tests_properties(validation::secure_channel_level::Sign_B256Sha256_2048bit PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=secure_channel_level_Sign_B256Sha256_2048bit.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::secure_channel_level::None "python3" "S2OPC_ROOT_DIR/tests/scripts/tap-wrap.py" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/test_secure_channels_server 2048" "--wait-server" "S2OPC_ROOT_DIR/bin/test_secure_channels_client" "none")
set_tests_properties(validation::secure_channel_level::None PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=secure_channel_level_None.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::secure_channel_level::Sign_B256_2048bit "python3" "S2OPC_ROOT_DIR/tests/scripts/tap-wrap.py" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/test_secure_channels_server 2048" "--wait-server" "S2OPC_ROOT_DIR/bin/test_secure_channels_client" "encrypt" "B256")
set_tests_properties(validation::secure_channel_level::Sign_B256_2048bit PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=secure_channel_level_Sign_B256_2048bit.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::secure_channel_level::SignAndEncrypt_B256Sha256_4096bit "python3" "S2OPC_ROOT_DIR/tests/scripts/tap-wrap.py" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/test_secure_channels_server 4096" "--wait-server" "S2OPC_ROOT_DIR/bin/test_secure_channels_client" "encrypt" "B256Sha256" "4096")
set_tests_properties(validation::secure_channel_level::SignAndEncrypt_B256Sha256_4096bit PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=secure_channel_level_SignAndEncrypt_B256Sha256_4096bit.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::secure_channel_level::SignAndEncrypt_B256Sha256_4096bit_server_vs_2048bit_client "python3" "S2OPC_ROOT_DIR/tests/scripts/tap-wrap.py" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/test_secure_channels_server 4096" "--wait-server" "S2OPC_ROOT_DIR/bin/test_secure_channels_client" "encrypt" "B256Sha256" "2048" "4096")
set_tests_properties(validation::secure_channel_level::SignAndEncrypt_B256Sha256_4096bit_server_vs_2048bit_client PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=secure_channel_level_SignAndEncrypt_B256Sha256_4096bit_server_vs_2048bit_client.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::secure_channel_level::SignAndEncrypt_B256Sha256_2048bit_server_vs_4096bit_client "python3" "S2OPC_ROOT_DIR/tests/scripts/tap-wrap.py" "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/bin" "--server-cmd" "S2OPC_ROOT_DIR/bin/test_secure_channels_server 2048" "--wait-server" "S2OPC_ROOT_DIR/bin/test_secure_channels_client" "encrypt" "B256Sha256" "4096" "2048")
set_tests_properties(validation::secure_channel_level::SignAndEncrypt_B256Sha256_2048bit_server_vs_4096bit_client PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=secure_channel_level_SignAndEncrypt_B256Sha256_2048bit_server_vs_4096bit_client.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::check_libsub "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/tests/ClientServer/interop_tools" "--server-cmd" "python3 S2OPC_ROOT_DIR/tests/ClientServer/interop_tools/server.py 25000" "./check_libsub")
set_tests_properties(validation::check_libsub PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=check_libsub.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
add_test(validation::check_wrapper "python3" "S2OPC_ROOT_DIR/tests/ClientServer/scripts/with-opc-server.py" "--server-wd" "S2OPC_ROOT_DIR/tests/ClientServer/interop_tools" "--server-cmd" "python3 S2OPC_ROOT_DIR/tests/ClientServer/interop_tools/server.py 25000" "./check_wrapper")
set_tests_properties(validation::check_wrapper PROPERTIES  ENVIRONMENT "CK_TAP_LOG_FILE_NAME=check_wrapper.tap" WORKING_DIRECTORY "S2OPC_ROOT_DIR/bin")
