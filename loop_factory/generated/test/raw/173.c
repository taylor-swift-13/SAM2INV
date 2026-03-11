int main1(){
  int z, zr, mv, a, j7, eh;

  z=1*5;
  zr=0;
  mv=21;
  a=0;
  j7=1;
  eh=0;

  while (1) {
      if (!(mv>0&&zr<z)) {
          break;
      }
      if (mv<=j7) {
          eh = mv;
      }
      else {
          eh = j7;
      }
      zr += 1;
      j7 += 1;
      a = a + eh;
      mv = mv - eh;
  }

}
