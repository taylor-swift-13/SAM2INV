int main1(int a,int b,int k,int m){
  int l, i, v;

  l=61;
  i=l;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a,Pre);
    loop invariant b == \at(b,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant l == 61;
    loop invariant i >= 0;
    loop invariant i <= 61;

    loop invariant (i == 61) ==> (v == \at(a, Pre));
    loop invariant (i != 61) ==> (v == 0);

    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant (i == 61) ==> (v == a);
    loop assigns v, i;
  */
  while (i>0) {
      if ((i%4)==0) {
          v = v+v;
      }
      else {
          v = v-v;
      }
      i = i/2;
  }

}