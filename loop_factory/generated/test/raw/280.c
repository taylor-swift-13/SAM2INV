int main1(){
  int rn4, nv5h, wy, po6k, jw, z6;

  rn4=1*2;
  nv5h=0;
  wy=23;
  po6k=0;
  jw=1;
  z6=0;

  while (wy>0&&nv5h<rn4) {
      if (wy<=jw) {
          z6 = wy;
      }
      else {
          z6 = jw;
      }
      po6k += z6;
      nv5h++;
      wy -= z6;
      jw = jw + 1;
  }

}
