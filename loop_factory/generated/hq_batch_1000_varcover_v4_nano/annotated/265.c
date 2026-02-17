int main1(int a,int b,int k,int n){
  int l, i, v, r, g;

  l=15;
  i=0;
  v=a;
  r=i;
  g=a;

  
  /*@

    loop invariant g == a;

    loop invariant l == 15;

    loop invariant 0 <= i <= l;

    loop invariant r == i * (2 + g);

    loop invariant (i % 2 == 0) ==> (v == a);

    loop invariant (i % 2 == 1) ==> (v == -1);

    loop assigns v, r, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      r = r-1;
      v = g-v;
      r = r+3;
      r = r+g;
      i = i+1;
  }

}