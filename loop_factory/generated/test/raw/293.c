int main1(){
  int cb, vsl, e, y, mp, ujw;

  cb=1+4;
  vsl=0;
  e=0;
  y=vsl;
  mp=vsl;
  ujw=-6;

  while (1) {
      if (!(e<cb)) {
          break;
      }
      y = cb-e;
      ujw = ujw + y;
      e += 1;
  }

  while (1) {
      if (!(cb<mp)) {
          break;
      }
      e = (mp)+(-(cb));
      e = e - e;
      cb += 1;
  }

}
