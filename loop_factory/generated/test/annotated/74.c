int main1(int a,int x){
  int td8, oh, o, nk9e, v6e;
  td8=a;
  oh=-3;
  o=a;
  nk9e=3;
  v6e=x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nk9e - o == 3 - a;
  loop invariant nk9e >= 3;
  loop invariant v6e == x + (nk9e - 3) * (td8 + 3);
  loop invariant (nk9e <= 3) ==> (v6e == x);
  loop invariant o == \at(a, Pre) + (nk9e - 3);
  loop invariant (oh == -3) || (oh == td8);
  loop assigns o, v6e, nk9e, oh;
*/
while (oh<td8) {
      o = (1)+(o);
      v6e = v6e+td8-oh;
      nk9e = nk9e + 1;
      oh = td8;
  }
}