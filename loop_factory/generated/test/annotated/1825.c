int main1(){
  int pzy8, qe1, mv, v, mh, m;
  pzy8=172;
  qe1=0;
  mv=qe1;
  v=pzy8;
  mh=pzy8;
  m=qe1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mv == pzy8 * qe1 * qe1;
  loop invariant pzy8 == 172;
  loop invariant m == 0;
  loop invariant mh == pzy8;
  loop invariant 0 <= qe1 <= pzy8;
  loop invariant v == pzy8 * (1 + 2 * qe1);
  loop assigns qe1, mv, v, mh;
*/
while (qe1 < pzy8) {
      qe1 += 1;
      mv += v;
      v = v + pzy8;
      v = v + mh;
      mh = mh + m;
  }
}