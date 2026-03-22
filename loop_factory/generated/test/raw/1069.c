int main1(int a){
  int r1, mjhb, kx, siul, tjt, p;

  r1=(a%35)+14;
  mjhb=r1;
  kx=(a%18)+5;
  siul=(a%15)+3;
  tjt=kx;
  p=0;

  while (kx!=0) {
      siul -= 1;
      kx = kx - 1;
      tjt = tjt + siul;
  }

  for (; p<=mjhb-1; p++) {
  }

}
