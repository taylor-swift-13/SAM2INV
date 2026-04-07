int main1(){
  int w, e5d, z, l7, wi, yz, oyos, pay;

  w=1*5;
  e5d=0;
  z=9;
  l7=14;
  wi=0;
  yz=w;
  oyos=w;
  pay=w;

  while (e5d<w) {
      if (wi==0) {
          z += 2;
          l7 -= 2;
          wi = 1;
      }
      else {
          z -= 2;
          l7 += 2;
          wi = 0;
      }
      e5d += 1;
      if (e5d+4<=oyos+w) {
          pay += oyos;
      }
      oyos = oyos+(e5d%2);
      yz = yz + 1;
      oyos = oyos - 1;
  }

}
