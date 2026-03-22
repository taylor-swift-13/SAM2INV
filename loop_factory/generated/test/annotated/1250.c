int main1(int c){
  int lt7, rym, f, r, tt, z6aa, b;
  lt7=171;
  rym=0;
  f=rym;
  r=lt7;
  tt=0;
  z6aa=lt7;
  b=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == lt7 + rym;
  loop invariant f == (r*(r+1)*(2*r+1))/6 - (lt7*(lt7+1)*(2*lt7+1))/6;
  loop invariant 0 <= rym <= lt7;
  loop invariant 6*f == (rym*(6*lt7*lt7)) + (6*lt7*rym*(rym+1)) + (rym*(rym+1)*(2*rym+1));
  loop invariant f == rym*lt7*lt7 + lt7*rym*(rym+1) + rym*(rym+1)*(2*rym+1)/6;
  loop invariant r == 171 + rym;
  loop invariant f == ((rym*(rym+1)*(2*rym+1))/6) + 171*rym*(rym+1) + 29241*rym;
  loop assigns r, f, z6aa, b, c, rym;
*/
while (1) {
      r = r + 1;
      f = f+r*r;
      z6aa = z6aa+(f%7);
      b = b+(r%9);
      c = c*3+(r%7)+1;
      c = c*c+tt;
      rym += 1;
      if (rym>=lt7) {
          break;
      }
  }
}