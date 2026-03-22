int main1(){
  int b, ypsh, su5, jfwt, d3p, c, ss;
  b=1+24;
  ypsh=0;
  su5=0;
  jfwt=1;
  d3p=6;
  c=0;
  ss=1*2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c <= b+1;
  loop invariant jfwt == 3*c*c + 3*c + 1;
  loop invariant su5 == c*c*c;
  loop invariant ss == 2;
  loop invariant c >= 0;
  loop invariant ypsh == 0;
  loop invariant d3p == 6 * (c + 1);
  loop invariant b == 25;
  loop assigns c, su5, jfwt, ss, d3p;
*/
while (c<=b) {
      c = c + 1;
      su5 = su5 + jfwt;
      jfwt = jfwt + d3p;
      ss += ypsh;
      d3p += 6;
  }
}