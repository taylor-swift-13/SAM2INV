int main1(int v){
  int b8, rq, p, hkyc, k4q;
  b8=116;
  rq=-4;
  p=5;
  hkyc=0;
  k4q=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (p - 2*hkyc) == 5;
  loop invariant k4q == (hkyc % 9);
  loop invariant rq <= b8;
  loop invariant (rq == -4) || (rq == b8);
  loop invariant ( (rq == -4 && p == 5 && hkyc == 0 && k4q == 0)
                    ||
                    ( rq == b8
                      &&
                      ( (v > 0  ==> (hkyc ==  1 && p == 7 && k4q ==  1))
                        &&
                        (v <= 0 ==> (hkyc == -1 && p == 3 && k4q == -1))
                      )
                    )
                  );
  loop invariant ((rq < b8) ==> (p == 5 && hkyc == 0 && k4q == 0));
  loop assigns hkyc, k4q, p, rq;
*/
while (rq < b8) {
      hkyc = (p = p + ((v>0)-(v<=0)), rq = rq + 1, hkyc + ((v>0)-(v<=0)));
      k4q = k4q+(hkyc%9);
      p = p + hkyc;
      rq = b8;
  }
}