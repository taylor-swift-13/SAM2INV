int main1(int a,int p,int q){
  int l, i, v, t, b, d;

  l=45;
  i=0;
  v=a;
  t=-6;
  b=i;
  d=a;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant b == 0;

    loop invariant t == -6;

    loop invariant v == a + i;


    loop invariant (i > 0) ==> (d == -a - (i - 1));

    loop invariant i <= l;

    loop assigns i, v, d;

    loop variant l - i;

  */
  while (i<l) {
      d = v+t+b;
      v = v+1;
      d = t-d;
      i = i+1;
  }

}