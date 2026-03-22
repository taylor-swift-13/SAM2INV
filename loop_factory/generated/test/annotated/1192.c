int main1(){
  int r9, h, vn, o0, cjo;
  r9=11;
  h=1+1;
  vn=0;
  o0=r9;
  cjo=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 2;
  loop invariant (cjo == o0*o0) || (cjo == -3);
  loop invariant o0 >= 11;
  loop invariant vn <= 0;
  loop assigns h, vn, o0, cjo;
*/
while (1) {
      if (!(h!=vn)) {
          break;
      }
      if (!(h<=vn)) {
          vn -= h;
          o0 += cjo;
      }
      else {
          h -= vn;
          cjo = cjo + o0;
      }
      o0 = o0*4+3;
      cjo = cjo*o0+3;
      cjo = o0*o0;
  }
}