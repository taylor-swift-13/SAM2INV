int main1(int a){
  int twd, oal, p1, z;

  twd=a-1;
  oal=0;
  p1=(a%28)+10;
  z=twd;

  while (p1>oal) {
      p1 -= oal;
      oal++;
      z += oal;
  }

}
