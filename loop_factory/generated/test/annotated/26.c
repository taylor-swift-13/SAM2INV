int main1(int n,int z){
  int xg, eg, f;
  xg=67;
  eg=xg;
  f=eg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 3*eg - 2*67;
  loop invariant z - \at(z, Pre) == eg - 67;
  loop invariant n - \at(n, Pre) == 67 * (eg - 67) + ((eg - 67) * (eg - 67 + 1)) / 2;
  loop invariant eg <= xg;
  loop invariant 67 <= eg;
  loop invariant \at(z, Pre) <= z;
  loop invariant eg >= 67;
  loop invariant z - eg == \at(z, Pre) - 67;
  loop invariant n >= \at(n, Pre);
  loop invariant f - 3*eg == -134;
  loop invariant xg == 67;
  loop invariant z == \at(z, Pre) + (eg - 67);
  loop invariant n == \at(n, Pre) + (eg - 67)*67 + ((eg - 67)*(eg - 66))/2;
  loop invariant f == 3*eg - 2*xg;
  loop invariant z - \at(z, Pre) == eg - xg;
  loop invariant z >= \at(z, Pre);
  loop invariant f == 3*eg - 134;
  loop invariant n == \at(n, Pre) + 67*(eg - 67) + ((eg - 67)*(eg - 66))/2;
  loop assigns f, eg, n, z;
*/
while (eg<xg) {
      f = f + 3;
      eg = eg + 1;
      n += eg;
      z += 1;
  }
}