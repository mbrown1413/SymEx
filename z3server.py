
import socket
import sys

import z3



HOST = '127.0.0.1'
PORT = 8000

s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

#Bind socket to local host and port
try:
    s.bind((HOST, PORT))
except socket.error as msg:
    print('Bind failed. Error Code : ' + str(msg[0]) + ' Message ' + msg[1])
    sys.exit()
    
print('Socket bind complete')

#Start listening on socket
try:
  s.listen(10)
  print('Socket now listening')

#now keep talking with the client
  while 1:
      #wait to accept a connection - blocking call
      conn, addr = s.accept()
      print('Connected with ' + addr[0] + ':' + str(addr[1]))
      sat_string = conn.recv(4096)
      print(sat_string)

      solver = z3.Solver()
      solver.add(eval(sat_string))
      result = solver.check().r
      if result == 1:
        conn.send("Y")
        print("Y")
      else:
        conn.send("N")
        print("N")

      conn.close()
      conn = None
      
finally:
  try:
    if conn:
      conn.close()
  finally:
    s.close()
