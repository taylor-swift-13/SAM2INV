int main1(){
  int z, o1, qcz;

  z=0;
  o1=(1%28)+10;
  qcz=-8;

  while (1) {
      if (!(o1>z)) {
          break;
      }
      o1 -= z;
      z += 1;
      qcz += z;
  }

}
