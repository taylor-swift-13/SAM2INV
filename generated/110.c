int main110(int z,int d,int u){
  int lcz, z7o, qer9, x8fd, qp;

  lcz=d-4;
  z7o=1;
  qer9=11;
  x8fd=1;
  qp=0;

  while (qer9>0&&x8fd<=lcz) {
      if (qer9>x8fd) {
          qer9 -= x8fd;
      }
      else {
          qer9 = 0;
      }
      x8fd = x8fd + 1;
      z7o = z7o + 1;
      qp = qp + 1;
      z = z + qp;
  }

}
