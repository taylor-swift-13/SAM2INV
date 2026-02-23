int main1(int m,int q){
  int t, j, h, x;

  t=(q%38)+17;
  j=t;
  h=q;
  x=2;

  while (j>=4) {
      if (h+4<=t) {
          h = h+4;
      }
      else {
          h = t;
      }
      h = h+1;
  }

}
