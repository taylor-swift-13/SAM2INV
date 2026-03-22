int main1(int e){
  int tipr, el, qvu5, ze, vd3, em, xr, eb;

  tipr=e;
  el=0;
  qvu5=0;
  ze=tipr;
  vd3=0;
  em=-4;
  xr=el;
  eb=e;

  while (qvu5<tipr&&ze>0) {
      ze -= 1;
      qvu5 += 1;
      if (el<em+1) {
          xr += em;
      }
      if (xr+6<tipr) {
          xr = xr + 1;
      }
      eb = eb + qvu5;
      em = em+tipr-el;
      eb = vd3+em+xr;
      vd3 += 1;
      if (em+5<tipr) {
          xr = xr + el;
      }
      else {
          e += 1;
      }
      em = em + 1;
  }

}
