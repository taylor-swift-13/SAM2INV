int main1(int b,int m,int n,int p){
  int l, i, v;

  l=27;
  i=l;
  v=b;

  
  /*@

    loop invariant i >= 0;

    loop invariant l == 27;

    loop invariant (v == 0) || (i == 27);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i <= 27;

    loop invariant i < 27 ==> v == 0;

    loop invariant i <= l;


    loop invariant (i == l) ==> (v == b);

    loop invariant (i < l) ==> (v == 0);

    loop invariant n == \at(n, Pre);

    loop invariant (i == 27) ==> (v == \at(b, Pre));

    loop invariant (i < 27) ==> (v == 0);

    loop invariant v == \at(b, Pre) || v == 0;

    loop assigns i, v;

    loop variant i;

  */
while (i>0) {
      v = v-v;
      i = i-1;
  }

}