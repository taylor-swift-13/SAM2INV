int main1(int y,int z){
  int fnb, n, sf, sh5j, tibt;

  fnb=z-7;
  n=0;
  sf=0;
  sh5j=-4;
  tibt=8;

  while (sf<fnb) {
      sf++;
      tibt = tibt + 1;
      n = n + y;
      y = y + sf;
  }

  while (fnb+7<=tibt) {
      n += sh5j;
      sh5j = sh5j+(n%4);
      z += n;
      tibt = (fnb+7)-1;
  }

}
