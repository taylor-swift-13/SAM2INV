int main1(int b,int k){
  int l, i, v, q;

  l=52;
  i=0;
  v=k;
  q=l;

  while (i<l) {
      q = q+q;
      q = q+v;
      i = i+5;
  }

  while (q<l) {
      q = q+1;
  }

}
