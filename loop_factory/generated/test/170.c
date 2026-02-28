int main170(int m,int p,int q){
  int n, i, l, s, c;

  n=q-6;
  i=0;
  l=i;
  s=q;
  c=p;

  while (1) {
      if (c<=s) {
          s = c;
      }
      l = l+1;
      l = l+s;
  }


  /*@ assert \false; */
}
