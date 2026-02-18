int main1(int a,int b,int k,int m){
  int l, i, v;

  l=61;
  i=l;
  v=a;

  while (i>0) {
      if ((i%4)==0) {
          v = v+v;
      }
      else {
          v = v-v;
      }
      i = i/2;
  }

}
