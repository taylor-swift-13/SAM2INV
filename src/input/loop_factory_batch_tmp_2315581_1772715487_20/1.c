int main1(int f){
  int rz, s5, qxzq, eb;

  rz=f+12;
  s5=0;
  qxzq=7;
  eb=0;

  while (s5<rz) {
      eb = s5%5;
      if (s5>=qxzq) {
          qxzq = (s5-qxzq)%5;
          qxzq = qxzq+eb-qxzq;
      }
      else {
          qxzq = qxzq + eb;
      }
      s5 = s5 + 1;
      f = f + eb;
  }

}
