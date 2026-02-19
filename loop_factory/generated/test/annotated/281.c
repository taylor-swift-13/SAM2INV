int main1(int m,int p){
  int l, i, v;

  l=39;
  i=0;
  v=l;

  
  /*@

    loop invariant l == 39;

    loop invariant 0 <= i <= l;

    loop invariant v == 0 || (i == 0 && v == l);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i <= l;

    loop invariant (i > 0) ==> (v == 0);

    loop invariant i >= 0;

    loop invariant (i == 0) ==> (v == l);

    loop invariant i > 0 ==> v == 0;

    loop invariant i == 0 ==> v == l;

    loop invariant 0 <= i && i <= l;

    loop invariant m == \at(m, Pre) && p == \at(p, Pre);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+4;
      v = v-v;
      i = i+1;
  }

}