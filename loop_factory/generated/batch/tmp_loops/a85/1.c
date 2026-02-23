int main1(int k,int m){
  int h, u, v, p;

  h=m-1;
  u=1;
  v=6;
  p=h;

  while (u<=h/3) {
      if (v+2<=h) {
          v = v+2;
      }
      else {
          v = h;
      }
  }

}
