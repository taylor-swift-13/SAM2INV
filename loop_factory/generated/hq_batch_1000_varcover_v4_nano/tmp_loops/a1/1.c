int main1(int k,int m,int n,int q){
  int l, i, v;

  l=m;
  i=l;
  v=2;

  while (i>0) {
      v = i*5;
      if ((i%5)==0) {
          v = v+3;
      }
      v = v-v;
      v = v+v;
      if (m<q+3) {
          v = v+1;
      }
      v = v+5;
      v = v+v;
      i = i/2;
  }

}
