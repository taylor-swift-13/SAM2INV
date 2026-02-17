int main1(int a,int b,int m,int q){
  int l, i, v, d, p;

  l=44;
  i=0;
  v=-4;
  d=b;
  p=q;

  while (i<l) {
      if (i%5==3) {
          v = v+1;
      }
      else {
          d = d+1;
      }
      if (i%5==4) {
          p = p+1;
      }
      else {
      }
      v = v+1;
      d = d-1;
      v = v+1;
      p = v-p;
      if ((i%8)==0) {
          d = d+i;
      }
  }

}
