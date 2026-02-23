int main1(int k,int n){
  int r, w, b, y, x, v;

  r=(k%12)+11;
  w=0;
  b=-2;
  y=4;
  x=k;
  v=w;

  while (w<r) {
      v = b+y+x;
      b = b+1;
      w = w+1;
  }

}
