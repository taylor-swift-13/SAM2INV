int main1(int b,int n,int p){
  int l, i, v, o;

  l=51;
  i=0;
  v=i;
  o=p;

  
  /*@

    loop invariant v == 2 * i;

    loop invariant 0 <= i && i <= l;

    loop invariant l == 51;

    loop invariant (i == 0 ==> o == \at(p,Pre));

    loop invariant (i >= 1 ==> o % 2 == 0);

    loop assigns i, v, o;

    loop variant l - i;

  */
while (i<l) {
      v = v+2;
      o = o+v;
      o = o+o;
      i = i+1;
  }

}