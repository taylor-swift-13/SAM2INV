int main1(int k,int n,int p,int q){
  int l, i, v;

  l=63;
  i=0;
  v=p;

  while (i<l) {
      if ((i%7)==0) {
          v = v+i;
      }
      else {
          v = v+1;
      }
      v = v+v;
      i = i+2;
  }

}
