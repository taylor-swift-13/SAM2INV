int main1(int v){
  int yo9i, fw, js, z0q, v3, x, ek, o;

  yo9i=38;
  fw=0;
  js=5;
  z0q=0;
  v3=0;
  x=13;
  ek=2;
  o=v;

  while (1) {
      if (!(fw<yo9i)) {
          break;
      }
      if (!(!(fw%2==0))) {
          if (js>0) {
              js = js - 1;
              z0q++;
          }
      }
      else {
          if (z0q>0) {
              z0q -= 1;
              js += 1;
          }
      }
      o = o + 3;
      v3++;
      fw += 1;
      x--;
      ek = ek + js;
      o = o + fw;
  }

}
