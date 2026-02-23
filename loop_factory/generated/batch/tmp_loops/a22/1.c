int main1(int a,int m){
  int h, u, v, b;

  h=19;
  u=h;
  v=m;
  b=-8;

  while (u>3) {
      if (v+1<=h) {
          v = v+1;
      }
      else {
          v = h;
      }
      v = v*3+3;
  }

}
