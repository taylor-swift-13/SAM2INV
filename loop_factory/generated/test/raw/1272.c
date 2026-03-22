int main1(){
  int ng, ok, e, plw, qaj;

  ng=1*3;
  ok=1;
  e=20;
  plw=3;
  qaj=-4;

  while (1) {
      if (!(ok*4<=ng)) {
          break;
      }
      e = e*4;
      plw = plw/4;
      qaj = qaj + e;
      ng = (ok*4)-1;
  }

}
