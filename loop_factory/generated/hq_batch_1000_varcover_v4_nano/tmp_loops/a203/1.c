int main1(int b,int k,int n,int q){
  int l, i, v, c;

  l=b-8;
  i=0;
  v=5;
  c=-3;

  while (i<l) {
      if (v+3<=l) {
          v = v+3;
      }
      else {
          v = l;
      }
      v = v+2;
      c = c+v;
  }

}
