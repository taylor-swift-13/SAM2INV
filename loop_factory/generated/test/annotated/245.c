int main1(int k,int p){
  int l, i, v, a, o;

  l=8;
  i=l;
  v=-4;
  a=k;
  o=p;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v <= -4;

    loop invariant v % 4 == 0;

    loop invariant k == \at(k, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant v % 2 == 0;

    loop invariant l == 8;


    loop assigns i, v;

  */
  while (i>0) {
        v = v*2;
        i = i-1;
  }

}