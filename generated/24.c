int main24(int x){
  int ks, e5, vdc, z, ahk, wi;

  ks=(x%25)+9;
  e5=0;
  vdc=1;
  z=1;
  ahk=x;
  wi=6;

  while (vdc<=ks) {
      z += 2;
      e5++;
      x = x+z+e5;
      vdc += z;
      wi = wi+z+z;
      ahk += 2;
  }

}
