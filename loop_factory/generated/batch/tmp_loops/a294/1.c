int main1(int a,int n){
  int y, i, c, v;

  y=n;
  i=0;
  c=a;
  v=-8;

  while (i<y) {
      if (c+4<=y) {
          c = c+4;
      }
      else {
          c = y;
      }
      c = c+v+v;
      c = c+1;
  }

}
