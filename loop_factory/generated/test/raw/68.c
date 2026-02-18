int main1(int b,int k,int n,int q){
  int l, i, v;

  l=45;
  i=0;
  v=-4;

  while (i<l) {
      v = v+1;
      if (i<l+5) {
          v = v+v;
      }
      else {
          v = v+1;
      }
      i = i+1;
  }

}
