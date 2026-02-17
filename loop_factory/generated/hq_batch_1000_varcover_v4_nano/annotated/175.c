int main1(int k,int m,int q){
  int l, i, v, s, a, d;

  l=70;
  i=1;
  v=q;
  s=q;
  a=-6;
  d=6;

  
  /*@

    loop invariant i - 2*v == 1 - 2 * \at(q,Pre);

    loop invariant i >= 1 && (i == 1 || i % 3 == 0);

    loop invariant (i == 1 && s == \at(q,Pre)) || (i > 1 && s >= 0);

    loop invariant k == \at(k,Pre) && m == \at(m,Pre) && q == \at(q,Pre);

    loop invariant i <= 3 * l;

    loop assigns v, s, i;

  */
while (i<l) {
      v = v+i;
      s = s*s;
      i = i*3;
  }

}