int main1(int p){
  int q, n, v, l;

  q=p+5;
  n=0;
  v=q;
  l=p;

  while (n<=q-1) {
      if (n<q/2) {
          v = v+l;
      }
      else {
          v = v+1;
      }
      l = l+l;
  }

}
