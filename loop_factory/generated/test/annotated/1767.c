int main1(){
  int qp5, jw, ll, gmf;
  qp5=1+9;
  jw=0;
  ll=0;
  gmf=jw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= jw <= qp5;
  loop invariant 6*ll == jw*(jw+1)*(2*jw+1);
  loop invariant (gmf % 4) == (ll % 4);
  loop invariant gmf >= 0;
  loop assigns jw, ll, gmf;
*/
while (jw < qp5) {
      jw = jw + 1;
      ll = ll + jw * jw;
      gmf = gmf*4+(ll%4)+0;
  }
}