int main1(int b,int m){
  int r, u, v;

  r=(b%30)+15;
  u=0;
  v=m;

  while (1) {
      v = v+2;
      if ((u%5)==0) {
          v = v+1;
      }
      if (u+4<=r+r) {
          v = v+1;
      }
  }

}
