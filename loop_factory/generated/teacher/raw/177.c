int main1(int k,int n){
  int c, q, l;

  c=65;
  q=c;
  l=c;

  while (q>=2) {
      l = l+q;
      l = l-l;
      q = q-2;
  }

}
