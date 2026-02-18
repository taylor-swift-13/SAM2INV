int main1(int b,int k,int n,int p){
  int l, i, v;

  l=58;
  i=0;
  v=-1;

  
  /*@

    loop invariant i <= l;

    loop invariant (i == 0) ==> (v == -1);

    loop invariant b == \at(b, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant l == 58;

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant (i == 0 ==> v == -1) && (i > 0 ==> v == 0) && (i <= l);

    loop invariant ((i == 0 && v == -1) || (i > 0 && v == 0));

    loop invariant (i == 0 && v == -1) || (i > 0 && v == 0);

    loop invariant i >= 0;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      v = v-v;
      i = i+1;
  }

}