int main1(int x){
  int py, is, d2z, c, ofzv;
  py=(x%35)+6;
  is=0;
  d2z=x;
  c=0;
  ofzv=py;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant py == ((\at(x, Pre) % 35) + 6);
  loop invariant c == (d2z - \at(x, Pre));
  loop invariant (x - \at(x, Pre)) == (4 * (d2z - \at(x, Pre)));
  loop invariant ofzv == (((\at(x, Pre) % 35) + 6) + (c * (c + 1)) / 2);
  loop invariant 0 <= c;
  loop invariant d2z == \at(x, Pre) + c;
  loop invariant ofzv == py + (c*(c+1))/2;
  loop invariant d2z - \at(x, Pre) == c;
  loop invariant x - \at(x, Pre) == 4 * c;
  loop invariant ofzv - py == c * (c + 1) / 2;
  loop invariant py == \at(x, Pre) % 35 + 6;
  loop invariant c >= 0;
  loop invariant (is == 0) || (is == py);
  loop invariant x == (\at(x, Pre) + 4*c);
  loop invariant ofzv == (py + (c*(c+1))/2);
  loop invariant d2z >= \at(x, Pre);
  loop invariant x >= \at(x, Pre);
  loop invariant (is == 0 || is == py);
  loop assigns d2z, c, ofzv, x, is;
*/
while (is<=py-1) {
      d2z += 1;
      c = (1)+(c);
      ofzv = ofzv + c;
      x += 4;
      is = py;
  }
/*@
  assert (py <= 0 ==> (c == 0 && d2z == \at(x, Pre) && ofzv == py && x == \at(x, Pre) && is == 0));
  assert (py >= 1 ==> (c == 1 && d2z == \at(x, Pre) + 1 && ofzv == py + 1 && x == \at(x, Pre) + 4 && is == py));
*/
}
