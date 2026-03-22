int main1(){
  int fw, m4r, ld, hv3, udu, v37;
  fw=1*5;
  m4r=fw+6;
  ld=(1%28)+8;
  hv3=(1%22)+5;
  udu=0;
  v37=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant udu + ld * hv3 == 54;
  loop invariant ld >= 9;
  loop invariant udu >= 0;
  loop invariant (v37 + 8) % m4r == 0;
  loop invariant ld % 9 == 0;
  loop invariant 0 <= hv3 <= 6;
  loop invariant v37 >= -8;
  loop invariant m4r == fw + 6;
  loop invariant fw == 5;
  loop assigns hv3, ld, udu, v37;
*/
while (hv3!=0) {
      if (hv3%2==1) {
          udu += ld;
          hv3--;
      }
      v37 = v37 + m4r;
      ld = 2*ld;
      hv3 = hv3/2;
  }
}