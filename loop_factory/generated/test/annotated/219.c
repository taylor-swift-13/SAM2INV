int main1(int p,int q){
  int l, i, v;

  l=45;
  i=l;
  v=i;

  
  /*@

    loop invariant l == 45;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant v == 0 || v == 45;

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i <= 45;

    loop invariant 0 <= i && i <= 45;

    loop invariant (i < 45) ==> (v == 0);

    loop invariant 0 <= i && i <= l;


    loop assigns v, i;

  */
while (i>0) {
      v = v*2;
      v = v%6;
      i = i/2;
  }

}