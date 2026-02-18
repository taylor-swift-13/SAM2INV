int main1(int a,int q){
  int l, i, v, m, g;

  l=70;
  i=0;
  v=q;
  m=-4;
  g=-8;

  
  /*@

    loop invariant l == 70;

    loop invariant a == \at(a, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i <= l;

    loop invariant (v != l) ==> ((v - q) % 2 == 0);

    loop invariant i >= 0;


    loop invariant i == 0;

    loop assigns v;

  */
  while (i<l) {
      if (v+2<=l) {
          v = v+2;
      }
      else {
          v = l;
      }
  }

}