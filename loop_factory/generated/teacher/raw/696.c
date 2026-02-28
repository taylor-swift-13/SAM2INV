int main1(int a,int k,int n,int q){
  int h, o, v, i;

  h=(k%8)+14;
  o=0;
  v=h;
  i=k;

  while (1) {
      if (o>=h) {
          break;
      }
      v = v+3;
      o = o+1;
      v = v+i+i;
  }

}
