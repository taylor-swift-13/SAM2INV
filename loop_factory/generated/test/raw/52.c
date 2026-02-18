int main1(int k,int m,int n,int q){
  int l, i, v;

  l=34;
  i=0;
  v=l;

  while (i<l) {
      v = v+5;
      v = v+6;
      if ((i%3)==0) {
          v = v+v;
      }
      i = i+3;
  }

}
