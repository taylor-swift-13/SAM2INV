int main1(int b,int m){
  int r, u, v;

  r=(b%30)+15;
  u=0;
  v=-5;

  while (u<r) {
      if ((u%5)==0) {
          v = v+v;
      }
      u = u+1;
  }

}
