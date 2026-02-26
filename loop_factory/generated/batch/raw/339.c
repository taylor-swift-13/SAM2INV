int main1(int p,int q){
  int l, i, v, e;

  l=q;
  i=0;
  v=-8;
  e=p;

  while (i<=l-4) {
      if (i<l/2) {
          v = v+e;
      }
      else {
          v = v+1;
      }
      v = v+5;
      e = e+1;
      e = e+i;
  }

}
