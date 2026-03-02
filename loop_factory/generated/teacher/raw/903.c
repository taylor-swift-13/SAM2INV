int main1(int m,int n){
  int y, w, v, h;

  y=n+19;
  w=1;
  v=0;
  h=0;

  while (v<y) {
      if (v<y/2) {
          h = h+1;
      }
      else {
          h = h-1;
      }
      v = v+1;
  }

}
