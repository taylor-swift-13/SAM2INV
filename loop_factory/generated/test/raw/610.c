int main1(){
  int ba, x, vl, e;

  ba=1*3;
  x=0;
  vl=6;
  e=ba;

  while (x+5<=ba) {
      if (x<ba/2) {
          vl = vl + e;
      }
      else {
          vl++;
      }
      ba = (x+5)-1;
  }

}
