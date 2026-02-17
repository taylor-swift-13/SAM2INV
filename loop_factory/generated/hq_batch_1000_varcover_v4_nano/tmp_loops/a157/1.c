int main1(int a,int b,int n,int q){
  int l, i, v, j, o, y, w;

  l=(a%38)+19;
  i=0;
  v=b;
  j=-1;
  o=3;
  y=-3;
  w=q;

  while (i<l) {
      if (i%2==1) {
          v = v+1;
      }
      else {
          j = j+1;
      }
      if (i%2==0) {
          o = o+1;
      }
      else {
      }
      y = v+j+o;
  }

}
