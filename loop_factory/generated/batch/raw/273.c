int main1(int k,int n){
  int r, w, b, y;

  r=(k%21)+13;
  w=1;
  b=-2;
  y=4;

  while (w<=r-1) {
      if (w<r/2) {
          b = b+y;
      }
      else {
          b = b+1;
      }
      b = b+5;
      y = y+3;
  }

}
